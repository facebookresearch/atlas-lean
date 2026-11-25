# Repeated Freivalds test on fixed seeds

Given $n \times n$ matrices $A$, $B$, $C$ over
$\mathbb{Z}/2$ and seeds $r_0, \dots, r_{k-1} \in (\mathbb{Z}/2)^n$, run the Freivalds trial on
$A$, $B$, $C$ with each seed $r_0, \dots, r_{k-1}$ in order, including the trials after a
rejection, and return the conjunction of their results (true when $k = 0$). The arithmetic cost
of the run is the sum of the costs of the $k$ trials.
