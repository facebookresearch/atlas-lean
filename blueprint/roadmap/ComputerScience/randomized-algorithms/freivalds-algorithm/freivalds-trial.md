# Freivalds trial

Given $n \times n$ matrices $A$, $B$, $C$ over
$\mathbb{F}_2 = \mathbb{Z}/2$, stored as arrays of rows, and a seed $r \in \mathbb{F}_2^n$, the
trial computes the column vectors $Br$, $A(Br)$ and $Cr$, each by accumulating matrix products
into a zero column, and returns true exactly when $A(Br) = Cr$. Its cost is the pair (number of
scalar multiplications, number of scalar additions), each multiply-add step counting one of each.

The coefficient domain is $\mathbb{F}_2$ by intentional specialization, not by a restriction in
the cited source.
