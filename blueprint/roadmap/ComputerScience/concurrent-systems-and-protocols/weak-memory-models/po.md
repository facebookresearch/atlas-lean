# Program order of an x86-TSO event structure

An event $e_1$ precedes an event $e_2$ in
program order when the instructions of $e_1$ and $e_2$ belong to the same processor and that of
$e_1$ has the smaller program-order index, or when $e_1$ precedes $e_2$ in intra-instruction
causality (Owens, Sarkar and Sewell, *TPHOLs 2009*, Section 3.2, `po_iico`).
