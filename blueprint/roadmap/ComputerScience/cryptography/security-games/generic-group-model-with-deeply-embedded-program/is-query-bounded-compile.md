# Compiled programs make at most numQueries queries

Let `L` be a type of labels with decidable equality. For every environment
`env` and program `p`, the compiled oracle computation `GProg.compile env p`
is query-bounded by `numQueries p`, so every run makes at most `numQueries p`
queries.
