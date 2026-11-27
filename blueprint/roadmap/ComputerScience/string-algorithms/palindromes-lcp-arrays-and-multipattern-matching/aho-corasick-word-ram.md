# Aho-Corasick on the word RAM with an integer alphabet

For keywords and text over the integer alphabet $\{0, \dots, \sigma - 1\}$, there is a deterministic word-RAM program that builds the array trie of the keyword set, computes failure links by breadth-first search, fills the full next-move table and output-link chains, and scans the text, reporting all occurrences, within $O\big((\|P\| + 1)\sigma + |P| + |t| + \mathrm{occ}\big)$ instructions, where $\|P\|$ is the total keyword length and $\mathrm{occ}$ the number of reported occurrences.

## Proof sketch

Trie construction and table filling cost $O(\|P\|\sigma)$; breadth-first failure computation is amortized by the failure-depth potential; scanning makes one table lookup per text letter plus one step per output link followed.

## Depends on

- [Aho–Corasick automaton construction and scanning time](../string-matching-specifications/the-ahocorasick-algorithm.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Specification of the Aho-Corasick failure and output functions](aho-corasick-failure-and-output.md)

## Sources

- A. V. Aho and M. J. Corasick, "Efficient String Matching: An Aid to Bibliographic Search", Communications of the ACM 18(6), 1975.
