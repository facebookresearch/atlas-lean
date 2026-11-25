# The CTL model checker as a Boolean decision procedure

Let $\mathcal{T}$ be a labelled
transition system with finitely many states and finitely many labels, decidable transitions and
decidable equality of states, and let $V$ be a decidable valuation of atoms at states. For a state
$s$ and a CTL formula $\varphi$, the model checker returns true exactly when $s$ belongs to the
set of states that the satisfaction-set algorithm computes for $\varphi$ in $\mathcal{T}$ under
$V$.
