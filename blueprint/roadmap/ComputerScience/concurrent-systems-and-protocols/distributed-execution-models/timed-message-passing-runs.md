# Timed message-passing runs

There are $N$ processors $p_1, \dots, p_N$ on a completely connected network, and each processor $p_i$ has a *buffer*, the set of messages sent to $p_i$ but not yet received. Each processor follows a deterministic protocol given by a state-transition diagram, possibly with infinitely many states, whose initial state is determined by the processor's initial value; at some point it may irreversibly decide on a value. In each step a processor executes one instruction: $\mathrm{Send}(m, p_j)$ places $m$ in the buffer of $p_j$, and $\mathrm{Receive}(p_i)$ removes some, possibly empty, set $S$ of messages from the buffer of $p_i$ and delivers them to $p_i$. After a Send the next state depends only on the current state; after a Receive it also depends on $S$.

Time is measured by an external real-time clock in integer steps, and at each tick some processors take one step. A *run* specifies the initial states and, for each real-time step, which processors take steps, the instruction each executes, and, for each Receive, the set of messages delivered. In an infinite run a message $m$ sent to $p_j$ is *lost* if $p_j$ executes infinitely many Receive instructions and $m$ is never delivered. A processor is *correct* in a run if it always performs the instructions of its protocol and, in an infinite run, takes infinitely many steps.

For an interval $I$ of real time, the *communication bound* $\Delta$ holds in $I$ if every message placed in the buffer of $p_j$ at a time $s_1 \in I$ is delivered by any $\mathrm{Receive}(p_j)$ executed at a time $s_2 \in I$ with $s_2 \ge s_1 + \Delta$, or earlier; the *processor bound* $\Phi$ holds in $I$ if every contiguous subinterval of $I$ containing $\Phi$ real-time steps contains a step of every correct processor.

## Sources

- C. Dwork, N. Lynch and L. Stockmeyer, "Consensus in the presence of partial synchrony", *Journal of the ACM* 35(2):288–323, 1988, Sections 2.1 and 2.3
