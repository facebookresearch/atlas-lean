# Weakly bisimilar states have the same set of weak labels

In a labelled transition
system with a silent label $\tau$, write $\Rightarrow$ for the reflexive-transitive
closure of the $\tau$-transition relation. The weak transitions
$s \stackrel{\mu}{\Longrightarrow} t$ are the trivial ones $s \stackrel{\tau}{\Longrightarrow} s$
and the composites $s \Rightarrow s_1 \xrightarrow{\mu} s_2 \Rightarrow t$; the saturated
system has the same states and has the weak transitions as its transitions. Two states are
weakly bisimilar if some bisimulation of the saturated system relates them.
If $s$ and $t$ are weakly bisimilar, then the set of labels $\mu$ with
$s \stackrel{\mu}{\Longrightarrow} s'$ for some $s'$ equals the set of labels $\mu$ with
$t \stackrel{\mu}{\Longrightarrow} t'$ for some $t'$.
