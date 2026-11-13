# Pointer jumping ranks every list in ⌈log₂ n⌉ rounds

Let $\mathrm{succ}$ be a successor map
on the nodes $0, \dots, n-1$ whose lists terminate. Then for every node $v$, entry $v$ of the table
returned by list ranking by pointer jumping, which runs $\lceil \log_2 n \rceil$ rounds, is the
rank of $v$.
