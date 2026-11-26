# Rail-limited feedback map

For real numbers $A$ (gain), $\beta$ (feedback factor), $v_{\min}$, $v_{\max}$ (rails) and $v_i$
(input), the rail-limited feedback map sends an output value $v_o$ to

$$F(v_o) = \operatorname{clamp}(v_{\min}, v_{\max}, A (v_i - \beta v_o)),$$

the [rail clamp](rail-clamp.md) of the amplified error. An operating point of the amplifier is a
fixed point $v_o = F(v_o)$; no dynamics are modelled. In the physical reading the feedback is
negative, $A > 0$ and $\beta > 0$, and the rails are ordered, $v_{\min} < v_{\max}$; the map is
defined for all real inputs.
