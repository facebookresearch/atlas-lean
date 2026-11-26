# Line currents of a delta connection

For complex branch currents `(I_ab, I_bc, I_ca)` of a delta connection, indexed by the integers
mod 3, the line currents are

`(I_a, I_b, I_c) = (I_ab - I_ca, I_bc - I_ab, I_ca - I_bc)`,

that is `J_p - J_{p-1}` at index `p` for the branch currents `J = (I_ab, I_bc, I_ca)`, with the
index taken mod 3. With the branch current `I_ab` directed from terminal `a` to terminal `b` (and
cyclically for the other branches) and each line current directed into its terminal, this is
Kirchhoff's current law at the three terminals.
