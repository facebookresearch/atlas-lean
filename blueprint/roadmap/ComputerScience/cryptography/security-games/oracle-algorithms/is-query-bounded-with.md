# Is Query Bounded With

A two-phase query bound: `IsQueryBoundedWith cont q c` holds when `c` makes some number
`j ≤ q` of queries along every path and its output `x` satisfies `cont x (q - j)`, the budget
left for the next phase.
