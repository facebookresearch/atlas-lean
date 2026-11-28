# Advisory and handoff criteria for human-in-the-loop controllers

Fix a human-in-the-loop controller as in the [controller model](human-in-the-loop-controller-model.md): an auto-controller $AC$ and an
advisory controller $VC$, both finite-state transducers, a human operator $HC$, the advisory signal $\mathit{auto}$ written by $VC$, and the
labelling $F$ of the states of $AC$ that marks the failure-prone states. Fix a positive integer $T$, the human response time counted in
transitions, and a cost function $C$ on controllers. The controller is:

1. **monitoring** if at every step the value of $\mathit{auto}$ is determined by the history of the run up to and including the current
   environment input, without prediction of later inputs;
2. **minimally intervening** if it minimizes $C$ among the admissible controllers; in the source, $C$ combines the probability that, once
   $\mathit{auto}$ is set to false, the environment eventually forces $AC$ into a failure-prone state with the cost of the human taking
   control, and its Theorem 1 uses the total weight of the mined assumption edges;
3. **$T$-prescient** if on every run, whenever $AC$ is in a failure-prone state at step $k$, $\mathit{auto}$ was set to false at some step
   $j \le k - T$;
4. **conditionally correct** if $F(q)$ is false whenever $\mathit{auto}$ is true while $AC$ is in state $q$, and, whenever $\mathit{auto}$
   changes from true to false while $AC$ is in state $q$, $F(q')$ is false for every state $q'$ reachable from $q$ within $T - 1$
   transitions.

These are predicates on the formal model; whether people comply is outside them. The source states criteria 1 and 2 in words; the forms
above are their precise readings.

## Depends on

- [Human-in-the-loop controller model](human-in-the-loop-controller-model.md)

## Sources

- W. Li, D. Sadigh, S. S. Sastry and S. A. Seshia, *Synthesis for Human-in-the-Loop Control Systems*, TACAS 2014, §3.3 (the four criteria) and Theorem 1 with Algorithm 1 (the cost function). <https://sites.bu.edu/depend/files/2017/02/hilp-tacas14.pdf>
