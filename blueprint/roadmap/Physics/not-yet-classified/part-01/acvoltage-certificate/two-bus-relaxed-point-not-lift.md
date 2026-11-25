# Two-bus relaxed point that is not a lift

Consider the two-bus current-limited optimal power flow problem with one unit-conductance branch and no shunts, active demand $(0, 15/16)$, zero reactive demand, active generation limits $[-2, 3]$ at bus $0$ and $[0, 0]$ at bus $1$, reactive generation limits $[-1, 1]$, squared voltage limits $[1/8, 4]$, squared current limit $4$ and cost coefficients $(1, 0)$. Take the dual witness with multiplier $4$ on the upper active limit at bus $1$, multiplier $9/16$ on the upper squared-voltage limit at bus $0$, all other multipliers zero, and factor $F = (5/4, -2)^{\mathsf T}$, and let

$$W = \begin{pmatrix} 4 & 2 \\ 2 & 17/16 \end{pmatrix}.$$

Then $W$ is feasible for the semidefinite relaxation, $W \neq VV^{\mathsf H}$ for every $V \in \mathbb{C}^2$, the relaxation cost of $W$ is $2$, and the certified bound of the witness is strictly less than the relaxation cost of $W$.
