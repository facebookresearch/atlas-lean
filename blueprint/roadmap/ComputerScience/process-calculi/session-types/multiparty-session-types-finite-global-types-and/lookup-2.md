# Lookup of a label in a local branch list

For a label type with decidable equality, the lookup of a label in a local branch list scans the list in order and returns the local continuation of the first entry carrying that label, or `none` if no entry carries it.
