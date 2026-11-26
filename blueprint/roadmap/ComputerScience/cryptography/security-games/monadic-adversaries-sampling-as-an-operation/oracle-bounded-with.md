# Oracle Bounded With

`OracleBoundedWith cont q c`: along every path, the monadic computation `c` makes at most `q`
**oracle queries**; sampling steps are free. The output `x` satisfies `cont x j` for the budget
`j` left (the two-phase form of `IsQueryBoundedWith`). Counting sampling steps as queries would
make a coin-tossing adversary look expensive; `SampleBoundedWith` counts those separately.
