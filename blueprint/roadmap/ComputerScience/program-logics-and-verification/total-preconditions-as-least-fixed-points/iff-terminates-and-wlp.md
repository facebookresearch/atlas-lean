# Total correctness is termination plus liberal correctness

For every deterministic IMP command $c$, postcondition $Q$ and state $s$, $\operatorname{wp}(c,Q)(s)$ holds exactly when there exists a final state $t$ with a big-step execution $c:s\Downarrow t$, and $\operatorname{wlp}(c,Q)(s)$ holds.
