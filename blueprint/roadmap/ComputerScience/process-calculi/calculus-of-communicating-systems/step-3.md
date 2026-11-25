# Transitions of static CCS

The labelled transition relation $P \xrightarrow{\alpha} P'$ on
static CCS processes, with actions $\alpha$ the CCS labels (silent $\tau$, inputs and outputs), is
the least relation closed under the following rules, where $\alpha.P$ is the prefix, $P + Q$ the
choice, $P \mid Q$ the parallel composition, $P \setminus L$ the restriction of $P$ by a finite
list $L$ of channel names, and $P[f]$ the relabelling of $P$ by a finite relabelling $f$. The
prefix has the transition $\alpha.P \xrightarrow{\alpha} P$. If $P \xrightarrow{\alpha} P'$, then
$P + Q \xrightarrow{\alpha} P'$, $Q + P \xrightarrow{\alpha} P'$,
$P \mid Q \xrightarrow{\alpha} P' \mid Q$ and $Q \mid P \xrightarrow{\alpha} Q \mid P'$. If
$P \xrightarrow{\alpha} P'$ and $Q \xrightarrow{\beta} Q'$ where $\alpha$ and $\beta$ are
complementary (an input and an output on the same channel), then
$P \mid Q \xrightarrow{\tau} P' \mid Q'$. If $P \xrightarrow{\alpha} P'$ and $\alpha$ is $\tau$ or
its channel is not in $L$, then $P \setminus L \xrightarrow{\alpha} P' \setminus L$. If
$P \xrightarrow{\alpha} P'$, then $P[f] \xrightarrow{f(\alpha)} P'[f]$, where $f(\tau) = \tau$, an
input on a channel $a$ is sent to the visible label $f(a)$ that $f$ assigns to $a$, and an output
on $a$ is sent to the complement of $f(a)$.
