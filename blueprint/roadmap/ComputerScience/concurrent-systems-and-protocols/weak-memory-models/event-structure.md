# Event structures of the axiomatic x86-TSO model

An event structure on a type $E$ of
events assigns to each event the processor $p$ and the program-order index $i \in \mathbb{N}$ of
its instruction, the $i$-th instruction of $p$, and its action: a read or a write of a value at a
memory address or at a register of a processor, or an MFENCE. It also carries an
intra-instruction causality relation on the events, and the atomicity data: a set of sets of
events, those of each LOCK'd instruction (Owens, Sarkar and Sewell, *TPHOLs 2009*,
Section 3).
