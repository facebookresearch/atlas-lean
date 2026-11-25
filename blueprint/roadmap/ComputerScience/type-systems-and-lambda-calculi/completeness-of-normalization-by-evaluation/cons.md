# Extending a related environment and substitution by one variable

Let $\xi$ be a semantic environment for a context $\Gamma$ in a context $\Delta$ that is
[syntactically related](syntactically-related.md) to a substitution $\sigma$ from $\Gamma$ to
$\Delta$, and let $a$ be a semantic value of type $A$ in $\Delta$ that is syntactically related
to a term $s$ of type $A$ in $\Delta$. Then the environment for $\Gamma$ extended by $A$ that sends
the new variable to $a$ and agrees with $\xi$ elsewhere is syntactically related to the
substitution that sends the new variable to $s$ and agrees with $\sigma$ elsewhere.
