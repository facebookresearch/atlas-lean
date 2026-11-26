# Computing small string attractors is NP-complete

For every fixed $k \ge 3$, the *$k$-attractor problem*, deciding for a string $T$ and an integer $t$ whether there is a set of $t$ positions crossed by some occurrence of every substring of length at most $k$, is NP-complete. Consequently computing $\gamma(T)$ is NP-hard.

## Proof sketch

Membership in NP is clear since a candidate set can be verified in polynomial time. For hardness, Kempa and Prezza reduce from a covering problem on graphs: vertices become gadgets over private letters and each edge becomes a short substring of length at most $k$ whose occurrences lie only near the gadgets of its endpoints, so that small attractors correspond to small covers.

## Depends on

- [String attractors](string-attractor.md)

## Proof depends on

- [String attractors](string-attractor.md)

## Sources

- Dominik Kempa, Nicola Prezza, "At the Roots of Dictionary Compression: String Attractors", STOC (2018), arXiv:1710.10964.
