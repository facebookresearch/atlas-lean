# Call-by-name reduction step of PCF

Write $\underline{n}$ for the numeral
$\mathrm{succ}^n\,\mathrm{zero}$, and $b[a]$ for the result of substituting the closed term $a$
for the bound variable of an abstraction body $b$. One-step call-by-name reduction $t \to t'$
between closed PCF terms of the same type is the least relation closed under these rules:
$f\,a \to f'\,a$ whenever $f \to f'$; $(\lambda b)\,a \to b[a]$, without evaluating $a$;
$\mathrm{succ}\,t \to \mathrm{succ}\,t'$, $\mathrm{pred}\,t \to \mathrm{pred}\,t'$ and
$\mathrm{ifz}\,t\,s_1\,s_2 \to \mathrm{ifz}\,t'\,s_1\,s_2$ whenever $t \to t'$;
$\mathrm{pred}\,\mathrm{zero} \to \mathrm{zero}$ and
$\mathrm{pred}\,\underline{n+1} \to \underline{n}$ for every natural number $n$;
$\mathrm{ifz}\,\mathrm{zero}\,s_1\,s_2 \to s_1$ and
$\mathrm{ifz}\,\underline{n+1}\,s_1\,s_2 \to s_2$ for every natural number $n$; and
$\mathrm{fix}\,t \to t\,(\mathrm{fix}\,t)$.
