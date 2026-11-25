# Feasible DC dispatch

A network has finitely many buses $v$, branches $e$ with tail and head buses and coefficients $b_e$, and generators $g$ located at buses. Let $A_{ve} = [\mathrm{tail}(e) = v] - [\mathrm{head}(e) = v]$, $L_b = A\,\mathrm{diag}(b)\,A^{\top}$, the DC branch flow $f(\theta) = \mathrm{diag}(b)\,A^{\top}\theta$, and $C_{vg} = 1$ if generator $g$ sits at bus $v$ and $0$ otherwise. Given demands $d$, a reference bus $r$, generator limits $p_{\min}, p_{\max}$ and flow limits $f_{\min}, f_{\max}$, a generation vector $p$ and bus angles $\theta$ form a feasible dispatch when

- $L_b\,\theta = C\,p - d$;
- $\theta_r = 0$;
- $p_{\min,g} \le p_g \le p_{\max,g}$ for every generator $g$;
- $f_{\min,e} \le f(\theta)_e \le f_{\max,e}$ for every branch $e$.
