# Irreducible suffix–prefix matches

An assembly string graph has the reads as vertices and an arc for every irreducible suffix–prefix match: an overlap that is not implied by two shorter-range overlaps through a third read. Characterizing transitive matches by a single irreducible match and a left-context suffix test lets them be discarded on the fly while all matches are enumerated in time linear in input plus output.

- [Transitive suffix–prefix matches and left contexts](transitive-suffix-prefix-matches-and-left-contexts.md)
