# Greedy overlap merge of a list of strings

For a list of strings over an alphabet with decidable equality, the merged string is the left fold of the overlap merge starting from the empty string. Merging $a$ with $b$ appends to $a$ the string $b$ with its first $k$ symbols dropped, where $k$ is the largest length such that the last $k$ symbols of $a$ equal the first $k$ symbols of $b$.
