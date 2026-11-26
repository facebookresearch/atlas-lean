# Right-hand sides of the relaxation constraints

For a
[current-limited AC optimal power flow problem](../current-limited-ac-optimal-power-flow-and-its-vo/current-limited-opf.md)
`P` (a network with branch and shunt admittances, fixed demands, generation limits, squared
voltage-magnitude bounds, squared branch-current limits and linear active-generation cost
coefficients `c_k`), the right-hand sides of the relaxation inequalities, in the order of the
[coefficient matrices](constraint-coeff.md), are, for bus `k`, `P_max,k - P_d,k`, `P_d,k - P_min,k`,
`Q_max,k - Q_d,k`, `Q_d,k - Q_min,k`, `v_max,k` and `-v_min,k` (generation limits shifted by the
demands `P_d`, `Q_d`, and the squared-voltage bounds), and, for branch `e`, the squared-current
limit `I²_max,e`. There are no equality constraints; a fixed generation is the pair of inequalities
`g ≤ P ≤ g`.
