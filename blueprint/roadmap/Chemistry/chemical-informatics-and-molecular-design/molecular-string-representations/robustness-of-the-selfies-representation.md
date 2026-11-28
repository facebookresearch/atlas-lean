# Robustness of the SELFIES representation

Decoding any finite string over the recognized tokens of one pinned library version builds an internal molecular graph admissible for that version's constraints. The claim is about that graph, before any SMILES text is written; serializing it and parsing the text back is a separate contract.

Pin the representation implemented by `selfies` 2.1.1: its recognized tokens (atom, branch, ring, the dot separator and the padding token), its default semantic constraint function $\nu$, and its decoder. *Internal decoding* is the construction the decoder performs before serialization: reading the token string as a queue, it creates one typed atom per emitted atom token, joins consecutive atoms with the demoted bond order of the chain layer, suspends and resumes the parent state at a branch token, queues a ring candidate at a ring token, restarts token derivation at a dot token, and finally resolves the queued candidates by the ring-closure fold. Write $\Gamma(\sigma)$ for the typed graph this construction returns on the token string $\sigma$: vertices are the emitted atoms with their descriptors, edges carry orders in $\{1,2,3\}$.

**Internal decoder soundness.** For every finite string $\sigma$ of recognized tokens, internal decoding terminates and $\Gamma(\sigma)$ is a $\nu$-admissible molecular graph. A string that emits no atom, among them the empty string and strings whose tokens are all skipped at the start symbol, returns the empty graph.

Graph admissibility is not serializer or parser correctness, and the distinction is not academic. Writing $\Gamma(\sigma)$ as SMILES text and reading that text back is governed by the serializer's ring-label allocation and by the tokenizer that consumes it, neither of which this statement covers: in the pinned release, a string of a hundred repetitions of the block `[C][C][C][Ring1][Ring1]` decodes to a hundred admissible three-membered rings, but the serializer allocates a distinct ring number per closure and emits `%100`, which a tokenizer consuming exactly two digits after `%` reads as `%10` followed by a further ring tag, so the text no longer denotes $\Gamma(\sigma)$. Nothing about toolkit acceptance, chemical stability, synthesizability or running time follows from the statement either.

Two features of the pinned decoder shape what can be proved. A ring token *reserves* a closure that the fold may still reject or cap: in `[C][Ring1][C]` the trailing atom token is read as the digit zero, so the candidate names the single atom twice and the fold rejects it as a self-loop. Admissibility therefore follows from budget safety at each resolved candidate, never from fulfilling every reservation. A dot token restarts token derivation; in the released version the atom indexing and the ring queue are shared across dots, so the ring candidate of `[C].[C][Ring1][C]` can target an atom of the preceding fragment, and the token guarantees no separation of the decoded graph into components.

Which molecular graphs arise as internal decoder outputs is a separate question and is not stated here: that set is defined as the image of $\Gamma$, so asserting that each member is decoded by some string would restate the definition. A witness for a particular graph comes from the round-trip statement of this chapter. The map $\Gamma$ is not injective: distinct strings return the same graph, and the padding token changes nothing.

## Depends on

- [Molecular graphs under valence constraints](molecular-graphs-under-valence-constraints.md)
- [The SELFIES chain-derivation grammar](selfies-derivation-grammar.md)
- [Branch and ring index encoding](branch-and-ring-index-encoding.md)
- [Ring-closure acceptance in a SELFIES derivation](ring-closure-acceptance-rule.md)

## Proof depends on

None.

## Expansion

The statement objects are not all available in this chapter, and that is what the hold records. The four linked pages give the chain layer, the index arithmetic and the deferred ring fold; they do not give the recognized semantic token domain or the full internal decoder, which also needs the recursive branch step with its start state $\mathbf{X}_{d_0}$ and consumption of $\min(N, \text{queue length})$ symbols, the budget reservation performed when a ring token is read, the dot restart with its shared atom indexing and ring queue, and the padding rule. A page that also spoke about SMILES text would need the serializer with its ring-label allocation and the parser, which are a further, separate contract.

Given the internal decoder, the proof is an induction over derivation steps whose invariant is that the current state carries at most one active attachment site with budget $i$, that each suspended branch frame records its parent's remaining budget, and that every atom stays within its budget as the fold resolves each queued candidate, which it may reject or cap. Termination follows because each step consumes at least one token of a finite string and the fold visits each candidate once.

## Context

Research-level statement over graduate machinery; the claim of Krenn, Häse, Nigam, Friederich and Aspuru-Guzik that makes SELFIES the search space of the generative and evolutionary models of this chapter, read here against the library version that defines the representation precisely.

## Sources

- Mario Krenn, Florian Häse, AkshatKumar Nigam, Pascal Friederich and Alán Aspuru-Guzik, *Self-referencing embedded strings (SELFIES): A 100% robust molecular string representation*, Machine Learning: Science and Technology 1 (2020) 045024, Abstract and Section 1, which advertise robustness. DOI [10.1088/2632-2153/aba947](https://doi.org/10.1088/2632-2153/aba947), arXiv:[1905.13741v2](https://arxiv.org/abs/1905.13741v2).
- Alston Lo, Robert Pollice, AkshatKumar Nigam, Andrew D. White, Mario Krenn and Alán Aspuru-Guzik, *Recent advances in the Self-Referencing Embedded Strings (SELFIES) library*, Digital Discovery 2 (2023) 897–908, Sections II–III for version 2.1.1 and its default constraints, Section III D (Eq. 16 and its footnote) and Section III E (Eq. 19) for the recursive branch step and the ring reservation that the fold may reject or cap, and Section IV for the token and interface domains. DOI [10.1039/d3dd00044c](https://doi.org/10.1039/d3dd00044c), PMC10408573.
