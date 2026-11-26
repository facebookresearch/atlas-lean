# For nonzero total impedance, fault voltage is E minus Thévenin drop

For complex $E$, $Z_{\mathrm{th}}$ and $Z_f$ with $Z_{\mathrm{th}} + Z_f \neq 0$, the
[fault voltage](fault-voltage.md) is also the source voltage minus the drop across the Thévenin
impedance:

$$V_f = E - Z_{\mathrm{th}}\, I_f,$$

where $I_f$ is the [fault current](fault-current.md). For $Z_{\mathrm{th}} + Z_f = 0$ and $E \neq 0$
this fails: both $V_f$ and $I_f$ are $0$ by the convention $x / 0 = 0$.
