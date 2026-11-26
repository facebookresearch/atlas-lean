# Deadlock-correct duality for universal until

Let $\varphi$ and $\psi$ be CTL formulas,
and write $s \models \chi$ when the state $s$ of a labelled transition system satisfies the
formula $\chi$ under a given valuation of the atoms. Then
$s \models \mathsf{A}[\varphi \mathbin{\mathsf{U}} \psi]$ if and only if neither
$s \models \mathsf{E}[\neg\psi \mathbin{\mathsf{U}} (\neg\psi \land (\neg\varphi \lor
\neg\mathsf{EX}\,\top))]$ nor $s \models \mathsf{EG}\,\neg\psi$.

Here $\neg\mathsf{EX}\,\top$ holds exactly at the deadlocked states, those with no outgoing
transition. So $\mathsf{A}[\varphi \mathbin{\mathsf{U}} \psi]$ fails at $s$ exactly when some
infinite run starting at $s$ stays in $\neg\psi$ forever, or some finite run starting at $s$ stays
in $\neg\psi$ up to a $\neg\psi$-state at which $\varphi$ fails or which is deadlocked.
