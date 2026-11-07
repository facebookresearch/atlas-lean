# Correctness of the CTL model checker

Let a labelled transition system have finitely many
states and finitely many labels, with decidable transitions and decidable equality of states, and
let the valuation of the atoms be decidable. For every CTL formula $\varphi$ and every state $s$,
the state $s$ lies in the set $\mathrm{sat}(\varphi)$ computed by the model checker if and only if
$s$ satisfies $\varphi$.

The proof is by induction on $\varphi$. The temporal cases use the correctness of the finite
fixed-point computations of $\mathsf{EU}$ and $\mathsf{EG}$, and the $\mathsf{AU}$ case also
identifies the computed bad-target set with the states satisfying the bad-target formula.
