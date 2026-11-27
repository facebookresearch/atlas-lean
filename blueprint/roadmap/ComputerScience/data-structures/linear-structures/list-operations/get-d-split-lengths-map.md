# Named chunk lookup uses the first occurrence

Let $\lambda$ assign a natural-number length to each name, let $N = [n_0, \dots, n_{m-1}]$ be a
list of names, let $L$ be a list, and let $a$ be a name occurring in $N$, with $j$ the position of
its first occurrence in $N$. Split $L$ at the lengths $\lambda(n_0), \dots, \lambda(n_{m-1})$
(consecutive chunks cut from the front of $L$, shorter once $L$ runs out). Then the chunk at
position $j$ (a default list is returned for positions out of range) is the list of the first
$\lambda(a)$ elements, or all of them if there are fewer, of the list obtained from $L$ by
dropping its first $\lambda(n_0) + \dots + \lambda(n_{j-1})$ elements.
