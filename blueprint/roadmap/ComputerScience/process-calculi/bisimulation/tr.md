# Weak bisimilarity answers a strong step with a weak step

Let $L$ be a labelled
transition system with a silent label $\tau$. A weak $\tau$-transition is a sequence of zero or
more $\tau$-steps, and for $\mu \ne \tau$ a weak $\mu$-transition is zero or more $\tau$-steps,
one $\mu$-step and zero or more $\tau$-steps. Two states are weakly bisimilar when some
bisimulation of the system whose $\mu$-transitions are the weak $\mu$-transitions of $L$ relates
them. If $p$ and $q$ are weakly bisimilar and $L$ has a transition from $p$ to $p'$ labelled
$\mu$, then there is a state $q'$ with a weak $\mu$-transition from $q$ to $q'$ such that $p'$
and $q'$ are weakly bisimilar.
