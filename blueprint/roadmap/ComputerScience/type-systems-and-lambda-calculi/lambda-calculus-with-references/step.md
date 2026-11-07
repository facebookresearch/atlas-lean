# One-step evaluation with references

One step of call-by-value evaluation
$t \mid \mu \to t' \mid \mu'$, from a term $t$ with a store $\mu$ to a term $t'$ with a store
$\mu'$, is the least relation closed under the following rules, in which $v$, $v_1$ and $v_2$ are
values. If $t \mid \mu \to t' \mid \mu'$, then $t\,t_2 \mid \mu \to t'\,t_2 \mid \mu'$,
$v_1\,t \mid \mu \to v_1\,t' \mid \mu'$,
$\mathsf{ref}\,t \mid \mu \to \mathsf{ref}\,t' \mid \mu'$, $!t \mid \mu \to {!t'} \mid \mu'$,
$t := t_2 \mid \mu \to t' := t_2 \mid \mu'$ and $v_1 := t \mid \mu \to v_1 := t' \mid \mu'$. The
application $(\lambda{:}T.\,s)\,v_2$ with store $\mu$ steps, with $\mu$ unchanged, to the result of
substituting $v_2$ for variable $0$ in $s$. The allocation $\mathsf{ref}\,v$ with store $\mu$ steps
to the location $n$, where $n$ is the length of $\mu$, and the store becomes $\mu$ with $v$
appended at the end. If $\mu$ has an entry $u$ at location $l$, then $!l \mid \mu \to u \mid \mu$.
If $l$ is less than the length of $\mu$, then $l := v \mid \mu \to \mathsf{unit} \mid \mu'$, where
$\mu'$ is $\mu$ with its entry at $l$ replaced by $v$.

## Sources

- TAPL Figure 13-1, with each fresh location allocated at the end of the store.
