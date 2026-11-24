# Setup timing model

One register-to-register path through the
circuit `c`: a clock edge at time `0` launches it and the next edge, at the
period `T`, captures it. The circuit inputs (the launching register's
outputs) settle at `inputArrival`, gate `j` has delay `delay j`, and output
arrival times are those of the gate-delay model. The capturing register's
setup constraint holds when every designated output settles at least the
setup time `ts` plus the clock uncertainty `u` before the capturing edge.
