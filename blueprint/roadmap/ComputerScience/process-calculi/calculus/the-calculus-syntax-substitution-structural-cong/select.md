# Branch selection in nested choices of the π-calculus

The relation "$Q$ is selectable from $P$" on [processes](proc.md) is the reflexive and transitive closure of the two branch selections $P + Q \rightsquigarrow P$ and $P + Q \rightsquigarrow Q$: $Q$ is obtained from $P$ by repeatedly discarding branches of choices. The selected process need not be guarded: for instance $\mathbf{0}$ is selectable from $\mathbf{0}$ and from $\mathbf{0} + P$.
