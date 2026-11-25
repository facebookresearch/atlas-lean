# Fundamental theorem of the reducibility relation

Let $t$ be a term of type $A$ in a
context $\Gamma$, and let $\sigma$ be a reducible substitution sending each variable of $\Gamma$
to a closed term of the same type. Then the closed term obtained by applying $\sigma$ to $t$ is
reducible.

The lambda case is the key: evaluate an arbitrary reducible
argument to a value, cross the beta step, and invoke the induction hypothesis
under the extended substitution.
