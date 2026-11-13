# Weak bisimilarity transfers weak traces

In a labelled transition system with a
silent label $\tau$, write $\Rightarrow$ for the reflexive-transitive
closure of the $\tau$-transition relation. The weak transitions
$s \stackrel{\mu}{\Longrightarrow} t$ are the trivial ones $s \stackrel{\tau}{\Longrightarrow} s$
and the composites $s \Rightarrow s_1 \xrightarrow{\mu} s_2 \Rightarrow t$; the saturated
system has the same states and has the weak transitions as its transitions. Two states are
weakly bisimilar if some bisimulation of the saturated system relates them.
Suppose $s$ and $t$ are weakly bisimilar and $s$ reaches $s'$ by a multistep transition of
the saturated system with label list $\mu_1, \dots, \mu_n$, that is, by weak transitions
$s \stackrel{\mu_1}{\Longrightarrow} \cdots \stackrel{\mu_n}{\Longrightarrow} s'$. Then $t$
reaches some $t'$ by a multistep transition of the saturated system with the same label list,
and $s'$ and $t'$ are weakly bisimilar.
