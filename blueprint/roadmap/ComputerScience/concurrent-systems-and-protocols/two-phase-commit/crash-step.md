# Transitions of two-phase commit with crashes

The protocol with crashes steps from a
state $s$ to a state $t$ by an action exactly in the following cases; in each step every other
part of the state is unchanged.

* Protocol actions, taken only by operational processes. An operational working participant may
  vote yes, after which it is prepared, or vote no, after which it is aborted. An operational
  waiting coordinator may decide commit when every participant is prepared, and decide abort
  when some participant has aborted. An operational prepared participant
  learns commit from an operational committed coordinator, and an operational prepared or
  working participant learns abort from an operational aborted coordinator.
* Timeouts. An operational waiting coordinator may decide abort, and an operational working
  participant may decide abort.
* Cooperative termination. An operational prepared participant $p$ may ask an operational
  participant $q$: if $q$ has committed, $p$ commits; if $q$ has aborted, $p$ aborts; if $q$ is
  working, $q$ aborts.
* Crashes and recovery. An operational process may crash. A crashed coordinator recovers, and
  aborts if it was waiting. A crashed participant recovers, and aborts if it was working.

A participant learns a decision from the coordinator only while the coordinator is operational:
a crash loses the decision messages the coordinator has not delivered.
