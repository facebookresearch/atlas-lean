# Rail clamp of a value between $v_{\min}$ and $v_{\max}$

For real numbers $v_{\min}$, $v_{\max}$ and $x$, the rail clamp is

$$\operatorname{clamp}(v_{\min}, v_{\max}, x) = \max(v_{\min}, \min(v_{\max}, x)).$$

For ordered rails $v_{\min} \le v_{\max}$ it is the memoryless output limiter with closed endpoints:
values $x \le v_{\min}$ give $v_{\min}$, values in $[v_{\min}, v_{\max}]$ (endpoints included) are
unchanged, and values $x \ge v_{\max}$ give $v_{\max}$. The formula is defined for all real inputs:
for inverted rails $v_{\min} > v_{\max}$ it gives $v_{\min}$ for every $x$.
