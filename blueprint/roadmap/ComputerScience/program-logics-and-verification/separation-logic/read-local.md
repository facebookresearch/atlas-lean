# Local rule for a heap read

Let $x$ and $y$ be variables, let $a$ and $v$ be natural
numbers, and let $p$ and $q$ be predicates on stores. Write $s[x := n]$ for the store that agrees
with $s$ except that it maps $x$ to $n$, and $a \mapsto v$ for the heap assertion that holds when
the heap is the single cell at address $a$ holding $v$. If every store $s$ satisfying $p$ has
$s(y) = a$ and $q(s[x := v])$, then the separation-logic triple for the heap read $x := [y]$
(which loads into $x$ the value stored at the address held in $y$) is valid with precondition
"$p(s)$ and $a \mapsto v$ holds at $(s, h)$" and postcondition "$q(s)$ and $a \mapsto v$ holds at
$(s, h)$", where $s$ is the store and $h$ the heap.
