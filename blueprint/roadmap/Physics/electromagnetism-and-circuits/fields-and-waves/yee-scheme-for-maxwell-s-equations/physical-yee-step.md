# Physical Yee Step

One step of the physical periodic Yee update, returning `(E_new, H_new)`:
`H_new = H - (dt / μ₀) D₋ E`, then `E_new = E - (dt / ε₀) D₊ H_new`.
