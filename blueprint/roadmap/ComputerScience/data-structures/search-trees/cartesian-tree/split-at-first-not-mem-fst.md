# Splitting at the first occurrence leaves the value out of the left part

Let $m$ be an
element of a type with decidable equality and let $xs$ be a list in which $m$ occurs. When $xs$ is
split at the first occurrence of $m$, the left part does not contain $m$.

Together with the reconstruction property (the left part, then $m$, then the right part give back
$xs$), this characterizes the split point, including how duplicates of $m$ are handled when
building Cartesian trees; reconstruction alone would hold for a split at any occurrence.
