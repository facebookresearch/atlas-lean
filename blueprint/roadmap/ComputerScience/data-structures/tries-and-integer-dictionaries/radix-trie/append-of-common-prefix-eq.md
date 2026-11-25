# When the common prefix is the second list, the first list extends it

Let $s$ and $t$ be
lists over a type with decidable equality. If the longest common prefix of $s$ and $t$ is $t$,
then $s$ is $t$ followed by the list obtained by dropping the first $|t|$ elements of $s$, where
$|t|$ is the length of $t$.
