# Chemical paths by string interpolation

Two molecules written as robust strings are joined by replacing, one at a time, the tokens where their padded strings differ. Every intermediate string decodes to an admissible graph, so the construction needs no learned latent space, but some intermediates decode to nothing.

Pin the representation implemented by `selfies` 2.1.1 and write $\Gamma(\sigma)$ for the internal molecular graph a token string $\sigma$ decodes to, before any SMILES text is written. A *substitution* replaces one token of a string by another recognized token. Let $\sigma$ and $\sigma'$ be strings for the two endpoint molecules, aligned to a common length by appending padding tokens to the shorter one, and let $D = \{j : \sigma_j \neq \sigma'_j\}$ be their differing positions, enumerated in a chosen order. The *substitution sequence* they define is

$$
\sigma = \sigma^{(0)}, \; \sigma^{(1)}, \; \dots, \; \sigma^{(L)} = \sigma' , \qquad L = |D| ,
$$

where $\sigma^{(j)}$ replaces, in $\sigma^{(j-1)}$, the token at the $j$-th position of $D$ by the one $\sigma'$ carries there. Consecutive strings differ by exactly one substitution. Its *decoded sequence* is $\Gamma(\sigma^{(0)}), \dots, \Gamma(\sigma^{(L)})$, and a *chemical path* is the subsequence a filter retains, for instance the one dropping intermediates that decode to the empty graph; between two retained neighbours there is then no longer exactly one substitution.

Intermediates can be empty even when both endpoints are not. Padding `[C]` to `[C][nop]` and taking the endpoint `[Branch1][O]` gives the sequence `[C][nop]`, `[Branch1][nop]`, `[Branch1][O]`: the first decodes to methane, the middle emits no atom, since a branch token met at the start symbol is skipped without reading an argument and the padding token is ignored, and the last decodes to water. So the decoded sequence passes through the empty graph while both endpoints are nonempty, and a usable path either admits the empty graph explicitly or filters it out.

Three further restrictions. Admissibility of each decoded intermediate is the internal decoder's contract; whether an intermediate's SMILES text round-trips through a serializer and parser is a separate question, and it is not claimed here, nor is any claim that intermediates pass chemical filters such as stability or synthesizability. This page states the substitution-only construction; the source's local neighbourhoods also use insertions and deletions, which change the length and are outside the alignment above. The path depends on the strings chosen for the endpoints and on the order of $D$, since a molecule has many strings; the source randomizes over both and selects intermediates by fingerprint similarity, because the number of differing positions is not a structural distance.

## Depends on

- [Molecular graphs under valence constraints](../../chemical-informatics-and-molecular-design/molecular-string-representations/molecular-graphs-under-valence-constraints.md)
- [The SELFIES chain-derivation grammar](../../chemical-informatics-and-molecular-design/molecular-string-representations/selfies-derivation-grammar.md)

## Proof depends on

- [Robustness of the SELFIES representation](../../chemical-informatics-and-molecular-design/molecular-string-representations/robustness-of-the-selfies-representation.md)

## Expansion

The internal decoding map $\Gamma$ is the statement object this page still lacks: the chain layer linked here does not define the decode of a string containing branch or ring tokens, which the witness above already uses, so the full internal decoder of the pinned version is a missing statement prerequisite and the page is held until it exists. Given it, a formal development defines substitutions, the alignment by padding, the enumeration of $D$ and the sequence as a fold, so that neighbouring strings differ in one position and the last string is $\sigma'$; admissibility of every decoded intermediate is internal decoder soundness applied pointwise, which is why the robustness statement is the proof prerequisite. The filter and its retained subsequence are part of the construction, not a consequence of it.

The joint-similarity score of this chapter is what the source maximizes when it selects a median molecule along such paths; no median scoring definition is stated here, so that score is context rather than a prerequisite.

## Context

Graduate. The interpolation construction of Nigam, Pollice, Krenn, dos Passos Gomes and Aspuru-Guzik, which performs on a robust string representation the operations usually credited to a learned latent space.

## Sources

- AkshatKumar Nigam, Robert Pollice, Mario Krenn, Gabriel dos Passos Gomes and Alán Aspuru-Guzik, *Beyond generative models: superfast traversal, optimization, novelty, exploration and discovery (STONED) algorithm for molecules using SELFIES*, Chemical Science 12 (2021) 7079–7090, Sections II B–II D, including insertions and deletions in local neighbourhoods, randomization over representations and the structural filtering of candidates. DOI [10.1039/d1sc00231g](https://doi.org/10.1039/d1sc00231g), PMC8153210.
- Alston Lo, Robert Pollice, AkshatKumar Nigam, Andrew D. White, Mario Krenn and Alán Aspuru-Guzik, *Recent advances in the Self-Referencing Embedded Strings (SELFIES) library*, Digital Discovery 2 (2023) 897–908, Section III D for the skipped branch token at the start symbol and Section IV for the ignored padding token. DOI [10.1039/d3dd00044c](https://doi.org/10.1039/d3dd00044c), PMC10408573.
