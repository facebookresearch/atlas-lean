# Pipeline

C3: length-`L` outstanding pipeline before the receipts of period `t`.
Coordinate `j` is the receipt scheduled at `t + j.val`: initial pipeline at
`t + j.val` when `t + j.val < L`, else the already-placed order
`t + j.val - L`. Empty (no coordinates) at `L = 0`.
