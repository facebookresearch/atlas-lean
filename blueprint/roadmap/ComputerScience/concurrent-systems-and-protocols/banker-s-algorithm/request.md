# Resource-request algorithm

Let $S$ be a system of claims and allocations with processes
$P$ and a finite set $R$ of resource types, let $a : R \to \mathbb{N}$ be the vector of free
resources, $L$ a list of pending processes, $p$ a process and $r : R \to \mathbb{N}$ the
resources that $p$ requests. The request is granted when $p$ occurs in $L$, $L$ has no
repetitions, $r \le \mathrm{need}(p)$ and $r \le a$ componentwise, where $\mathrm{need}(p)$ is
the remaining need of $p$ in $S$, and the banker's safety algorithm succeeds for the system
obtained from $S$ by granting $r$ to $p$, from the free vector $a - r$ (componentwise truncated
subtraction) and the list $L$. A granted request returns the free vector $a - r$ and that
system; otherwise the algorithm returns no result.

No result covers the error case of the textbook algorithm (a request beyond the remaining
claim), the cases where the process must wait, and malformed input (a requester that is not
pending, or a pending list with repetitions).
