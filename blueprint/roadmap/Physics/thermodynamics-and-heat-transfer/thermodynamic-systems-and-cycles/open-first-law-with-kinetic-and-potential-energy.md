# Open first law with kinetic and potential energy

Consider a control volume of fixed shape with stored energy $E = U + K + \Phi$ (internal, kinetic and potential), inlet and outlet
streams with mass flows $\dot m_k \ge 0$, specific enthalpy $h_k$, speed $v_k$ and height $z_k$, heat input $\dot Q$ and shaft work
done by the contents on the surroundings $\dot W_s$. Assume the energy balance: the rate of accumulation of $E$ equals the energy
carried in by the streams minus that carried out, plus the heat added, plus the work done on the contents, where the work of the
streams at the ports is $\dot m_k P_k/\rho_k$ and no boundary moves. Then

$$E' = \sum_{\mathrm{in}} \dot m_k\Bigl(h_k + \tfrac12 v_k^2 + g z_k\Bigr) - \sum_{\mathrm{out}} \dot m_k\Bigl(h_k + \tfrac12 v_k^2 + g z_k\Bigr)
+ \dot Q - \dot W_s,$$

with the steady ($E' = 0$), no-flow ($E' = \dot Q - \dot W_s$) and adiabatic ($\dot Q = 0$) cases. Dropping a stored or a stream kinetic
or potential term is an approximation justified for that term alone, by its own smallness or constancy: a steady nozzle has $E' = 0$
while its stream kinetic terms are essential. Since $H = U + PV$ gives $H' = U' + (PV)'$,
replacing $U'$ by $H'$ requires $(PV)' = 0$; a constant volume (incompressible contents) leaves $(PV)' = V P'$, which is not zero
when the pressure changes.

## Depends on

## Proof depends on

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 6.1, Equations 6.2–6.5 (pp. 273–275), where $\dot W$ is the work done on the system; Section 6.2, the step from Equation 6.7 to Equation 6.8 via $dH = dU + P\,dV + V\,dP$ (p. 276).
