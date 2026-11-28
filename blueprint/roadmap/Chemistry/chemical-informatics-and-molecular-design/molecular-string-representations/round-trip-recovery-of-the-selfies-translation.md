# Round-trip recovery of the SELFIES translation

Encoding a supported SMILES string whose encoding lies in the internal decoder's recognized token domain and decoding the result returns the same molecule as the encoder's own preprocessed parse, compared as internal graphs with chirality projected out. Whether the decoded graph also survives being written as text and read back is a separate serialization question.

Pin the representation implemented by `selfies` 2.1.1, with encoder $\mathrm{enc}$, internal decoding $\Gamma$ and default constraint function $\nu$. Let $K(s)$ be the *encoder's preprocessed parse* of a SMILES string $s$: the molecular graph the encoder's own parsing and kekulization step produces, whose vertices are the atoms of $s$ typed by element, isotope, charge and explicit hydrogen count, and whose edges carry orders in $\{1,2,3\}$, aromatic bonds resolved by that step's deterministic assignment. Let $\pi$ forget chirality tags, and let $s$ be *supported*: an input the strict encoder accepts under its documented constraints, which excludes constructs the representation does not model, among them the wildcard atom `*` and the quadruple bond `$`, and for which $K(s)$ is $\nu$-admissible. In addition, require $\mathrm{enc}(s)$ to lie in the separately specified domain of $\Gamma$: a well-formed string over the recognized semantic tokens of version 2.1.1 with the same constraint function. In particular, its emitted branch and ring index tokens must use supported widths $1,2,3$ with their argument tokens. This is a token-domain condition, not an assumption that decoding recovers $K(s)$; strict encoder acceptance alone does not establish it. Under these hypotheses,

$$
\pi\big(\Gamma(\mathrm{enc}(s))\big) \;\cong\; \pi\big(K(s)\big) ,
$$

with $\cong$ isomorphism of molecular graphs preserving the remaining atom descriptors and the bond orders.

The comparison is between internal graphs. Serializing $\Gamma(\mathrm{enc}(s))$ and parsing the result is a further contract that supportedness of $s$ does not buy: a hundred concatenated copies of `C1CC1` in one component are accepted by the strict encoder, since the parser pops each ring tag at its closure and every atom stays within its capacity, yet the serializer then allocates a hundred distinct ring numbers and emits `%100`, which a tokenizer consuming exactly two digits after `%` reads as `%10` followed by another ring tag, so the text does not parse back to the decoded graph. A textual statement therefore needs the serializer's label allocation and the parser as named objects, with a bound on ring labels under which they agree; this page makes no such claim.

Two further scope notes. Chirality is projected out rather than asserted: the released encoder inverts an atom's `@`/`@@` tag when relocating a ring neighbour by an odd permutation, and the decoder places ring bonds before the ordinary outgoing bonds, so what survives is oriented stereochemistry relative to a neighbour ordering, which would need a permutation-aware predicate this page does not introduce. $K(s)$ is the encoder's own preprocessed parse with the deterministic assignment that step makes, not an arbitrary Kekulé structure, and no uniqueness of Kekulé assignments is claimed; the source's benzene example shows only that an aromatic input returns a Kekulé structure.

## Depends on

- [Molecular graphs under valence constraints](molecular-graphs-under-valence-constraints.md)
- [The SELFIES chain-derivation grammar](selfies-derivation-grammar.md)

## Proof depends on

None.

## Expansion

The expansion must specify three statement objects: the encoder's preprocessing with its deterministic kekulization, the projection $\pi$, and the full internal decoder with its recognized-token domain, recursive branch step, ring reservation, dot restart and padding rule. The encoder/decoder domain compatibility must cover branch token lengths and ring offsets, not just atom counts. These objects are required statement prerequisites; the serializer and output parser are outside this internal-graph theorem.

The proof then pairs the encoder's traversal with the decoder's construction: the encoder walks $K(s)$ and emits one atom token per vertex, branch tokens with the index encoding for the side chains and ring tokens for the non-tree edges, and internal decoding rebuilds the same vertices, descriptors and orders. Formalizing it needs the encoder's traversal normal form, which is the remaining proof prerequisite. Internal decoder soundness is a different claim and is not used here, and the benzene example verifies one case rather than the statement.

## Context

Graduate. The correctness contract relied on whenever a dataset is converted to SELFIES for training and the generated strings are converted back.

## Sources

- Alston Lo, Robert Pollice, AkshatKumar Nigam, Andrew D. White, Mario Krenn and Alán Aspuru-Guzik, *Recent advances in the Self-Referencing Embedded Strings (SELFIES) library*, Digital Discovery 2 (2023) 897–908, Sections II–III for version 2.1.1 and its default constraints, and Section IV A for the documented encoder and decoder contract, the separation of invalid from unsupported inputs, and the aromatic-to-Kekulé benzene example. DOI [10.1039/d3dd00044c](https://doi.org/10.1039/d3dd00044c), PMC10408573.
