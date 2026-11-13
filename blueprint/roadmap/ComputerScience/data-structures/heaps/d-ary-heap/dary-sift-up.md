# $d$-ary sift-up

Let $d \ge 2$, let $a$ be an array over a linearly ordered type, of length
$|a|$ with entries $a_0, \dots, a_{|a|-1}$, let $i$ be a natural number, and write
$p(i) = \lfloor (i-1)/d \rfloor$ for the parent of $i > 0$. The sift-up of $a$ from $i$ is defined
recursively: if $0 < i < |a|$ and $a_i < a_{p(i)}$, it is the sift-up from $p(i)$ of the array
obtained from $a$ by swapping the entries at positions $i$ and $p(i)$; otherwise it is $a$.
