# Merge Hi Gallop B equation

Public equation for the B half of a backward gallop.  It pins the exact
`gallop_left(temp, left, nb, nb - 1)` call and CPython's conversion from its
insertion index to the copied suffix length, `bCount = nb - index`.
