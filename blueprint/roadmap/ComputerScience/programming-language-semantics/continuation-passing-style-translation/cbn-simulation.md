# Plotkin's simulation theorem for the call-by-name CPS translation

Fix an answer type
$R$, and write $\overline{M}$ for the call-by-name CPS translation of a term $M$ and $T^*$ for
the translation of a type $T$. Let $M$ be a closed term of type $A \to B$ that evaluates to
$\lambda x.\,N$ under call-by-name big-step evaluation. Then for every closed value $K$ of type
$(A \to B)^* \to R$ and every closed term $w$ of type $R$, the application $\overline{M}\,K$
evaluates to $w$ under call-by-value big-step evaluation if and only if
$K\,(\lambda x.\,\overline{N})$ does.

This is the big-step form of the theorem, for the simply typed calculus.
