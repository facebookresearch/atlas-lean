# Pushing onto a $d$-ary heap leaves it ready for sifting up

Let $\alpha$ be a linearly
ordered type, let $d \ge 2$, and let $a$ be an array over $\alpha$ that is $d$-ary heap ordered,
with size $|a|$. Then for every $x \in \alpha$, the array obtained by appending $x$ to $a$ is
ready for $d$-ary sifting up at index $|a|$, the position of $x$; in particular every nonroot
entry other than $x$ is at least its $d$-ary parent.
