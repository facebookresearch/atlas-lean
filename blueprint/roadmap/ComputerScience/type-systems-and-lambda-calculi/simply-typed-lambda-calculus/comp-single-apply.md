# Composing a single substitution with a substitution

Let $a$ be a term of type $A$ in a
context $\Gamma$ and $\sigma$ a substitution from $\Gamma$ to $\Delta$, and write $a[\sigma]$ for
the result of applying $\sigma$ to $a$. The composite of the single substitution of $a$ for the
newest variable followed by $\sigma$ agrees, at every variable $x$ of the context $\Gamma$
extended by a newest variable of type $A$, with the extension of $\sigma$ that sends the newest
variable to $a[\sigma]$.
