# Call-by-name evaluation is preserved by the CPS translation

Fix an answer type $R$,
and write $\overline{M}$ for the call-by-name CPS translation of a term $M$ and $T^*$ for the
translation of a type $T$. Let $M$ and $V$ be closed terms of type $T$ such that $M$ evaluates
to $V$ under call-by-name big-step evaluation. Then for every closed value $K$ of type
$T^* \to R$ and every closed term $w$ of type $R$, the application $\overline{M}\,K$ evaluates to
$w$ under call-by-value big-step evaluation if and only if $\overline{V}\,K$ does.
