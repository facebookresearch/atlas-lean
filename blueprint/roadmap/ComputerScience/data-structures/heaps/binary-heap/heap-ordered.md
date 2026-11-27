# Heap order on a level-order array

An array $a$ over a type with a relation $\le$, indexed
from $0$, is heap ordered when every entry other than the root is at least its parent entry:
for every index $i$ with $0 < i < |a|$, where $|a|$ is the length of $a$, we have
$a_{\lfloor (i-1)/2 \rfloor} \le a_i$.
