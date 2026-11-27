# Strong bisimilarity implies weak bisimilarity

In a labelled transition system with a
silent label $\tau$, write $\Rightarrow$ for the reflexive-transitive
closure of the $\tau$-transition relation. The weak transitions
$s \stackrel{\mu}{\Longrightarrow} t$ are the trivial ones $s \stackrel{\tau}{\Longrightarrow} s$
and the composites $s \Rightarrow s_1 \xrightarrow{\mu} s_2 \Rightarrow t$; the saturated
system has the same states and has the weak transitions as its transitions. Two states are
weakly bisimilar if some bisimulation of the saturated system relates them.
If two states are bisimilar in the original system, then they are weakly bisimilar.
