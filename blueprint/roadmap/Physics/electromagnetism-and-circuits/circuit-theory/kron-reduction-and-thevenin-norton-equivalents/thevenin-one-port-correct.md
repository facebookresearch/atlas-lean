# Thevenin equivalent of a one-port with positive conductance

Let `K > 0` and `j_eff` be real, and consider the one-port law `K V = j_eff − I`, with port
conductance `K`, effective injected current `j_eff`, port voltage `V` and load current `I` flowing
out of the port. Then:

- the [Thevenin voltage](thevenin-voltage.md) is `V_th = j_eff / K` and the
  [Thevenin resistance](thevenin-resistance.md) is `R_th = 1 / K > 0`;
- for all real `V` and `I`, the one-port law holds exactly when `V = V_th − R_th I`;
- on open circuit, `K V = j_eff − 0` implies `V = V_th`;
- for every resistive load `V = R_L I` with `R_L ≥ 0`, the short circuit included, the one-port
  law implies `V = V_th R_L / (R_th + R_L)`.
