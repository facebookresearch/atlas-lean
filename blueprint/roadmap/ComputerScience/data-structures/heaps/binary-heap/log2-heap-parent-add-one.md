# The heap parent is one level up

For every natural number $i > 0$, the parent index
$p = \lfloor (i-1)/2 \rfloor$ satisfies
$\lfloor \log_2(p+1) \rfloor + 1 = \lfloor \log_2(i+1) \rfloor$; that is, in the level-order
binary tree the parent of a nonroot index lies one level above it.
