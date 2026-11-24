# At most one prefix of a score list ends at its first ladder epoch

For a list of real scores and lengths `j` and `k` at most its length, if the prefixes of lengths
`j` and `k` both [end at the first strict ascending ladder epoch](is-first-ladder.md) of their
walks, then `j = k`. The statement asserts uniqueness only: a list need not have such a prefix (for
example if all its partial sums are `≤ 0`). The bounds on `j` and `k` matter, since every `j` at
least the length gives the whole list.
