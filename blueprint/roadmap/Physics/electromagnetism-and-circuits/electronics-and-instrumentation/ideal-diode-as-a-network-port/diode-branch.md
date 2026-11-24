# Diode on a network branch in either orientation

Let a network have a finite set of nodes and a finite set of branches, each branch $e$ with a
tail and a head, branch voltages $v$ and branch currents $i$ (the current $i_e$ flows from tail to
head), and let $I_s, n, k_B, T, q$ be real. A diode with anode at node $a$ and cathode at node $c$
occupies branch $e$ when

- the branch joins the two nodes in either orientation: tail $a$ and head $c$, or tail $c$ and
  head $a$; and
- $i_e = s\, I_D(s\, v_e)$, where $I_D$ is the [diode current](diode-current.md) and $s$ is the
  entry at node $a$ and branch $e$ of the
  [electrical incidence](../../../../GraphTheory/algebraic-graph-theory/part-01/oriented-incidence-matrices/oriented-incidence.md),
  $s = [\mathrm{tail}(e) = a] - [\mathrm{head}(e) = a]$ ($[\cdot]$ is $1$ when the
  condition holds and $0$ otherwise).

For $a \ne c$, $s = +1$ when the anode is the tail, so $i_e = I_D(v_e)$, and $s = -1$ when the
anode is the head, so $i_e = -I_D(-v_e)$. If $a = c$ (a loop branch at $a$), then $s = 0$ and the
condition forces $i_e = 0$.
