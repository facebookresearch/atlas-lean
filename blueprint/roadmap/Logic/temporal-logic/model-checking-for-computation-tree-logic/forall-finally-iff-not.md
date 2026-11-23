# Deadlock-correct duality for AF

In a labelled transition system with a valuation of
atoms, let $\varphi$ be a CTL formula. A state $s$ satisfies $\mathsf{AF}\,\varphi$ if and only
if $s$ satisfies neither $\mathsf{E}[\neg\varphi \,\mathsf{U}\, (\neg\varphi \wedge
\neg\mathsf{EX}\,\top)]$ nor $\mathsf{EG}\,\neg\varphi$.

This is the case $\mathsf{A}[\top \,\mathsf{U}\, \varphi]$ of the duality for universal until.
The formula $\neg\mathsf{EX}\,\top$ holds exactly at deadlocked states, so the first disjunct
catches finite maximal paths that end at a deadlock without reaching $\varphi$.
