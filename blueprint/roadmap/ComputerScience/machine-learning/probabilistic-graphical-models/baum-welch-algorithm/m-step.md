# The Baum-Welch M-step

Let $h$ be a valid HMM with finite state set $S$ and finite
observation set $O$, let $x_0, \dots, x_{N-1}$ be observation sequences, and consider state paths
$(z_0, \dots, z_T)$. Write $I(s)$, $A(s, s')$ and $E(s, o)$ for the expected numbers, under the
posterior of $h$ and summed over the sequences, of sequences starting in $s$, of transitions
$s \to s'$ and of emissions of $o$ from $s$. The M-step is the HMM with real weights whose initial
weight of $s$ is $I(s) / N$, whose transition weight from $s$ to $s'$ is
$A(s, s') / \sum_{s''} A(s, s'')$, and whose emission weight of $o$ from $s$ is
$E(s, o) / \sum_{o'} E(s, o')$ (a quotient by $0$ is read as $0$).
