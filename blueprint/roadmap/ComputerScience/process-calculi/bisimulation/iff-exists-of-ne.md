# Weak transitions with a visible label

In a labelled transition system with a silent
label $\tau$, write $\Rightarrow$ for the reflexive-transitive closure of the
$\tau$-transition relation. A weak transition $s \stackrel{\mu}{\Longrightarrow} t$ is either
the trivial one $s \stackrel{\tau}{\Longrightarrow} s$ or a composite
$s \Rightarrow s_1 \xrightarrow{\mu} s_2 \Rightarrow t$. For a label $\mu \ne \tau$,
$s \stackrel{\mu}{\Longrightarrow} t$ holds if and only if there are states $s_1, s_2$ with
$s \Rightarrow s_1$, $s_1 \xrightarrow{\mu} s_2$ and $s_2 \Rightarrow t$.
