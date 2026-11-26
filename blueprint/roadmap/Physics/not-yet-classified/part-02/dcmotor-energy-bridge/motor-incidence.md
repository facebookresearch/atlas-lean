# DC motor loop incidence matrix

The ground-deleted, head-positive incidence matrix of the series DC motor loop is

$$B = \begin{pmatrix} -1 & 1 & 0 & 0 \\ 0 & -1 & 1 & 0 \\ 0 & 0 & -1 & 1 \end{pmatrix},$$

with rows indexed by the nodes $0$ (supply terminal), $1$ (resistance/inductance junction), $2$ (inductance/back-EMF junction) and columns by the branches, given as (head, tail): $0$ supply source (ground, node $0$), $1$ armature resistance (node $0$, node $1$), $2$ armature inductance (node $1$, node $2$), $3$ back-EMF source (node $2$, ground).
