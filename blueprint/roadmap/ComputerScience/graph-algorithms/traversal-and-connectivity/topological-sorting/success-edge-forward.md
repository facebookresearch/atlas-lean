# A successful topological sort points every edge forward

If Kahn's topological sort on a
finite directed graph $G$ returns a success with list $L$, then for every edge $u \to v$ of $G$ the
first position of $u$ in $L$ is strictly smaller than the first position of $v$ in $L$.
