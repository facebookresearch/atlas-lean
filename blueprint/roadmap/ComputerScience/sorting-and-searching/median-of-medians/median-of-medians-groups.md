# Group medians for median-of-medians selection

Given a list $xs$ over a linear
order, split $xs$ into consecutive blocks of five elements, the last of which may be shorter.
Sort each block $g$ by insertion sort and return, in block order, the entry at position
$\lfloor (|g| - 1)/2 \rfloor$ (counting from $0$) of each sorted block, that is, its lower
median. The cost is the total number of comparisons made by these insertion sorts.
