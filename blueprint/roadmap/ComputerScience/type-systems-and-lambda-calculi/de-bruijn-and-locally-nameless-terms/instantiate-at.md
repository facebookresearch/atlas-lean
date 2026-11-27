# Substitution for one index

`instantiateAt depth arg t` replaces the index `depth` of `t`,
counted from outside the abstractions of `t` around it, by `arg` shifted by `depth` and by those
abstractions, and lowers every larger index by one.
